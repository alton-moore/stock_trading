

/* Alton Moore, 956-581-5577 cell/SMS, aomoore3@gmail.com                                                          */
/* This program has been written to solve the problem given on page http://www.rgmadvisors.com/problems/orderbook  */
/*                                                                                                                 */
/* The problem description doesn't give much detail on how much error checking might be advisable.  This sort of   */
/* data stream, over modern communications networks, shouldn't suffer from corruption, so I would tend to avoid    */
/* doing much error checking.  Then again, if the company's business is live trading, and there is money at stake, */
/* such error checking should be considered mandatory.  The fact that input errors are merely skipped over belies  */
/* this, though, so I will not go to all that much trouble to look for errors in the input data stream, and tasks  */
/* such as validating the format of a timestamp or the uniqueness of an order ID may or may not be performed at    */
/* this point in the life of the program.  Suffice it to say that more diligence could certainly be applied in     */
/* the area of error checking if it were warranted/required.                                                       */
/*                                                                                                                 */
/* In general, the program is going to read each input line, set pointers to the data fields (and terminate them)  */
/* in the input buffer, and work with skip-lists, which are not susceptible to the unbalanced-tree problems like   */
/* sequential adds and rebalancing that (balanced) binary trees are, and which this input data would cause.        */
/* Totals will be kept alongside the lists; although this is duplicate data, speed considerations probably warrant */
/* this, and the DEBUG flag can be set to check the program's operation in regard to this duplicate data.          */
/*                                                                                                                 */
/* Three lists are kept: One by order ID, which is mainly used to look up the side of orders being reduced or      */
/* removed, one by price ascending, holds 'S'ell orders, and one by price descending, which holds 'B'uy orders.    */
/* Note that there is only one entry in each of the price lists for a given price, instead of an entry             */
/* corresponding to each order_id, since there is really no reason to maintain anything more than the price and    */
/* share quantity as an aggregate.  This also makes these lists fairly small, at only one entry per price.         */
/*                                                                                                                 */
/* In the interest of avoiding rounding errors, the program is entirely devoid of float functions and fields.      */
/* This leads to some fairly mechanical-looking manipulations of strings and long integers, but it works well.     */
/*                                                                                                                 */
/* How nice; I found a set of skip-list routines, and don't have to write my own. :-)  I had to modify them a bit. */
/* One may notice stylistic differences in the skip-list routines; I left some of the original style in homage.    */
/* I tried different list depth settings, but the number 15 seemed to work fine overall, so I left it for now.     */
/* This constant (the number 15) can be eliminated from the program by by using log(n), where n is the expected    */
/* maximum number of orders in play at any given time, but in the absence of that information, the 15 will do.     */
/*                                                                                                                 */
/* This program is written for 64 bit architecture.  sprintf() lines with "%0*ld" need to be changed to "%0*lld"   */
/* to run under 32 bit compilers.  I suppose that could be made automatic.                                         */


#include <stdlib.h>
#include <stdio.h>
#include <string.h>


/*---------- Program-specific variable definitions ----------*/

// General program variables
#define DEBUG 0       // Set this to non-zero to institute various debug outputs and program consistency checks.  Search for "DEBUG" to find them.
#define KEYLENGTH 10  // I added the key to the skip-list routines, and we'd like the length to be settable in the program somewhere.  Please note
                      // that the code which reverses the key (by subtracting price from 9999999999) still doesn't use this constant yet.

char input_buffer[100];  // This is used to read the lines from stdin.
long target_size;        // This holds the value of the parameter passed on the command line.

// These pointers are using for parsing the input line in place.
char *timestamp_pointer;       // Field one of each input line.
char *operation_type_pointer;  // 'A'dd or 'R'educe order amount
char *order_id_pointer;        // Unique order identifier; currently used only by 'R'educe order commands.
char *side_pointer;            // This is a 'B'uy or 'S'ell order.
char *price_pointer;           // This is the limit price of this order.
char *size_pointer;            // When adding orders, this is the share count.  When reducing an order amount, this is the amount to reduce by.

// Miscellaneous variables which are used locally here and there.
char temp_string[100];
int  temp_counter;
long temp_long;                // For use in DEBUG statements and the like.
char key_string[KEYLENGTH+1];  // Used for building and passing the key to the skip-list routines.  The extra byte is for a terminating null.
long returned_price;           // Used for receiving the value returned by the routine which traverses nodes to place/fill an order.
char dollar_string[16];        // Used for returning the value of the subroutine print_cents_as_dollars(), instead of passing a pointer back.

// List entry fields
struct list_entry_struct_type
{
char timestamp[10];
char order_id[6];
char side[1];
long price;  // In cents
long size;   // Number of shares
}  list_entry;  // Define this variable so we can work on this data.

long current_ask_count=0, previous_ask_count=0;  // We will track these figures here in spite of the fact that some of this is duplicate data,
long current_bid_count=0, previous_bid_count=0;  // because tallying up the figures from the lists after every operation would be, well, slow.
long previous_bid_price=0,previous_ask_price=0;  // These two variables are used only for deciding whether the price has changed and we should print something.

// Create some working variables for passing values on from the input-processing code to the output-determining code.
char side[1];
long price;  // In cents
long size;   // Number of shares


/*---------- Skip-list data structure data and subroutines ----------*/

// Skip-list variable definitions (see note below about origin of these skip-list routines)

/* define data-type and compare operators here */
#define MAXLEVEL 15   // Maximum number of levels in the skip-list.  A few test runs seem to indicate that this number is good.
#define compLT(a,b) (strncmp(a,b,KEYLENGTH) <  0)
#define compEQ(a,b) (strncmp(a,b,KEYLENGTH) == 0)
typedef struct Node_ {
    char                          key[KEYLENGTH];  /* 10 character key          */
    struct list_entry_struct_type data;            /* user's data               */
    struct Node_                  *forward[1];     /* skip-list forward pointer */
} Node;
typedef struct {
    Node *hdr;                  /* list Header */
    int listLevel;              /* current level of list */
} SkipList;
SkipList list_by_order_id,list_by_price_ascending,list_by_price_descending;  /* skip-list information */
Node *list_pointer;  // This is for working with list entries as we add them, look them up, and the like.


// Skip-list subroutines, found on the internet, modified to handle several lists (list is passed as an argument), added key/data separation, and added several routines.

void initList(SkipList *list)
{
int i;
if ((list->hdr = malloc(sizeof(Node) + MAXLEVEL*sizeof(Node *))) == 0)
    {
    fputs("insufficient memory to init list\n",stderr);
        exit(10);
    }
for (i = 0; i <= MAXLEVEL; i++)
    list->hdr->forward[i] = list->hdr;
list->listLevel = 0;
}

Node *insertNode(SkipList *list,char key[], struct list_entry_struct_type data)
{
int i, newLevel;
Node *update[MAXLEVEL+1];
Node *x;
/* find where data belongs */
x = list->hdr;
for (i = list->listLevel; i >= 0; i--)
    {
    while (x->forward[i] != list->hdr && compLT(x->forward[i]->key, key))
        x = x->forward[i];
    update[i] = x;
    }
x = x->forward[0];
if (x != list->hdr && compEQ(x->key, key))  // Is this key already on file?  If so, just return 0 instead of adding the value to the list,
    return(0);                              // since duplicate keys are not allowed by these routines.
/* determine level */
for (newLevel = 0; rand() < RAND_MAX/2 && newLevel < MAXLEVEL; newLevel++);
if (newLevel > list->listLevel)
    {
    for (i = list->listLevel + 1; i <= newLevel; i++)
        update[i] = list->hdr;
    list->listLevel = newLevel;
    }
/* make new node */
if ((x = malloc(sizeof(Node) + newLevel*sizeof(Node *))) == 0)
    {
    fputs("insufficient memory inserting node into list\n",stderr);
    exit(11);
    }
strncpy(x->key,key,KEYLENGTH);
x->data = data;
/* update forward links */
for (i = 0; i <= newLevel; i++)
    {
    x->forward[i] = update[i]->forward[i];
    update[i]->forward[i] = x;
    }
return(x);
}

void deleteNode(SkipList *list,char key[])
{
int i;
Node *update[MAXLEVEL+1], *x;
/* find where key belongs */
x = list->hdr;
for (i = list->listLevel; i >= 0; i--)
    {
    while (x->forward[i] != list->hdr && compLT(x->forward[i]->key, key))
        x = x->forward[i];
    update[i] = x;
    }
x = x->forward[0];
if (x == list->hdr || !compEQ(x->key, key))
    return;
/* adjust forward pointers */
for (i = 0; i <= list->listLevel; i++)
    {
    if (update[i]->forward[i] != x)
        break;
    update[i]->forward[i] = x->forward[i];
    }
free (x);
/* adjust header level */
while ((list->listLevel > 0) && (list->hdr->forward[list->listLevel] == list->hdr))
    list->listLevel--;
}

Node *findNode(SkipList *list,char key[])
{
int i;
Node *x = list->hdr;
for (i = list->listLevel; i >= 0; i--)
    {
    while (x->forward[i] != list->hdr && compLT(x->forward[i]->key, key))
        x = x->forward[i];
    }
x = x->forward[0];
if (x != list->hdr && compEQ(x->key, key))
    return (x);
return(0);
}

Node *firstNode(SkipList *list)
{
return(list->hdr->forward[0]);
}

//Node *lastNode(SkipList *list)  // Code included for consistency with firstNode(), but not used, so commented out for now.
//{
//int i;
//Node *x = list->hdr;
//for (i = list->listLevel; i >= 0; i--)
//    {
//    while (x->forward[i] != list->hdr)
//        x = x->forward[i];
//    }
//return (x);
//}

Node *nextNode(SkipList *list, Node *current_node)
{
if (current_node->forward[0] == list->hdr)
    return(0);
return(current_node->forward[0]);
}


/*---------- Program-level subroutines ----------*/

void reduce_size_or_delete_node(SkipList *list,char key[],long size)  // Fairly self explanatory name here....
{
Node *list_pointer;
long new_size;
//
if (!(list_pointer = findNode(list,key)))  // Failure to look up this entry?  Some sort of problem!
  {
  fputs("Problem looking up entry in list.\n",stderr);
  exit(20);
  }
new_size = list_pointer->data.size - size;
if (new_size < 0)
  {
  printf("New size < 0, so quitting, since the program should never allow this to happen.\n");
  exit(21);
  }
if (new_size > 0)
  list_pointer->data.size = new_size;  // The order was reduced but not eliminated, so just update its size.
else
  deleteNode(list,key);       // The order was reduced to 0.
}

long total_price_from_list(SkipList *list,long target_size)  // Returns price of first x shares in list in cents.
{
long shares_remaining=target_size;
long total_price_in_cents=0;
Node *list_pointer=firstNode(list);
//
while (((target_size - shares_remaining) < target_size) && (list_pointer))
  {
  if (list_pointer->data.size >= shares_remaining)  // Does this node hold enough shares to fulfill the request for x shares?
    {
    //if (DEBUG)
    //  printf("This node (%ld/%ld) holds enough to fulfill the rest of the request (%ld).\n",list_pointer->data.size,list_pointer->data.price,shares_remaining);
    total_price_in_cents += shares_remaining * list_pointer->data.price;  // Add to total and break out.
    break;
    }
  //if (DEBUG)
  //  printf("%ld shares remaining.  Using this entire node (%ld/%ld) to fulfill request, then moving on to the next.\n",shares_remaining,list_pointer->data.size,list_pointer->data.price);
  total_price_in_cents += list_pointer->data.size * list_pointer->data.price;  // Use all the shares in the current node.
  shares_remaining -= list_pointer->data.size;                                 // Reduce the shares remaining by the size of the current node, of course.
  list_pointer = nextNode(list,list_pointer);
  }
if (DEBUG)
  printf("Returning total price in cents of %ld for %ld shares.\n",total_price_in_cents,target_size);
return(total_price_in_cents);
}

void print_cents_as_dollars(long cents)  // This is the fairly mechanical conversion from long cents to a dollar amount in string form.
{
// A lot of trouble just to print something, but it certainly gets rid of those pesky floats and their potential computational inaccuracies throughout the program.
char temp_string[16];
if (cents < 100)      // This shouldn't happen in this program, but we'll be thorough anyway and ensure a minimum length of 3.
  sprintf(temp_string,"%03ld",cents);
else
  sprintf(temp_string,"%ld",cents);
dollar_string[0] = 0;
strncpy(dollar_string,temp_string,strlen(temp_string)-2);
dollar_string[strlen(temp_string)-2] = 0;
strcat(dollar_string,".");  // All this trouble just to insert this one decimal point!  Well, almost.  :-)
strcat(dollar_string+strlen(temp_string)-1,temp_string+strlen(temp_string)-2);
}

long list_total_size(SkipList *list)  // For use only when DEBUG is turned on.
{
Node *list_pointer=firstNode(list);
long list_total=0;
while (list_pointer)
  {
  list_total += list_pointer->data.size;
  list_pointer = nextNode(list,list_pointer);
  }
return(list_total);
}

long list_total_price(SkipList *list)  // For use only when DEBUG is turned on.
{
Node *list_pointer=firstNode(list);
long list_total=0;
while (list_pointer)
  {
  list_total += list_pointer->data.size * list_pointer->data.price;
  list_pointer = nextNode(list,list_pointer);
  }
return(list_total);
}


/*------------------------------ Main Program ------------------------------*/
int main(int argc,char *argv[])
{
if (DEBUG)
  fputs("DEBUG is on; expect volumninous output on the stdout channel.\n",stderr);

// Initialize the skip-list data structures.
initList(&list_by_order_id);          // 
initList(&list_by_price_ascending);   // 
initList(&list_by_price_descending);  // 


/*---------- Parse command line argument(s) ----------*/
if (argc != 2)  // 1st argument is always program name; make sure that second (target size) has been supplied, but no more.
  {
  fputs("Invalid argument count; syntax:  ./Pricer ###          where ### is target size to use\n",stderr);
  exit(1);
  }
target_size = strtol(argv[1],(char **)NULL,10);  // Convert 1st passed argument to an integer.
if (!target_size)  // Rudimentary error handling, but sufficient for this purpose.
  {
  fputs("Invalid argument; must be a long integer.\n",stderr);
  exit(2);
  }

/*-------------------- Main Loop --------------------*/
while (1)
  {
  fgets(input_buffer,sizeof(input_buffer)-1,stdin);  // Accept input from stdin.  If this buffer isn't big enough, something's wrong with the input!
  if (feof(stdin))
    break;
  if (!input_buffer[0])  // Empty string?  That can't be right!
    {
    fputs("Empty input string!  Ignoring.\n",stderr);
    continue;
    }
  if (DEBUG)
    printf("Input string: %s\n",input_buffer);

  // Get the timestamp, operation type, and order id from the input line and proceed accordingly.
  if ((timestamp_pointer = strtok(input_buffer," \n")) == NULL)  // Extract timestamp from input line.
    {
    fputs("No string found; continuing.\n",stderr);
    continue;
    }
  if ((operation_type_pointer = strtok(NULL," \n")) == NULL)     // Extract operation type from input line.
    {
    fputs("No operation type field found; continuing.\n",stderr);
    continue;
    }
  if ((order_id_pointer = strtok(NULL," \n")) == NULL)     // Extract order id from input line.
    {
    fputs("No order id field found; continuing.\n",stderr);
    continue;
    }

  // Now decide what course to take depending upon the value of the operation_type we found.

  if (operation_type_pointer[0] == 'A')  // Add order to book.
    {
    if ((side_pointer = strtok(NULL," \n")) == NULL)     // Extract side from input line.
      {
      fputs("No side field found; continuing.\n",stderr);
      continue;
      }
    if ((price_pointer = strtok(NULL," \n")) == NULL)     // Extract price from input line.
      {
      fputs("No price field found; continuing.\n",stderr);
      continue;
      }
    if ((size_pointer = strtok(NULL," \n")) == NULL)     // Extract size from input line.
      {
      fputs("No size field found; continuing.\n",stderr);
      continue;
      }
    sprintf(key_string,"%*s",KEYLENGTH,order_id_pointer);  // Right justify the order ID so it sorts correctly and can be used as a key.
    //
    // Now populate this list entry's fields.
    strcpy(list_entry.timestamp,timestamp_pointer);
    strncpy(list_entry.order_id,order_id_pointer,10);
    list_entry.side[0] = side_pointer[0];
    list_entry.price =  strtol(price_pointer,(char **)NULL,10) * 100;  // Convert up to the period, then multiply by 100 to make room for the cents that we'll add on.
    if (strchr(price_pointer,'.'))                                     // If a period is present in the input amount, then add the cents too.  This assumes two digits to the right of the decimal point, though, which is reasonable for dollar amounts.
      list_entry.price += strtol(strchr(price_pointer,'.')+1,(char **)NULL,10);
    list_entry.size  = strtol(size_pointer,(char **)NULL,10);
    //
    // Add to appropriate lists; all entries go into the order_id list, but into only one of the price lists.
    //
    insertNode(&list_by_order_id,key_string,list_entry);  // The 1st KEYLENGTH characters of key_string are the key and list_entry is the data.
    //
    if (list_entry.side[0] == 'S')  // We want to buy from lowest price to highest, so offers to sell go into this list.
      {
      sprintf(temp_string,  "%0*ld",KEYLENGTH,list_entry.price);  // Convert price to a string with length of KEYLENGTH.
      if (!(list_pointer = findNode(&list_by_price_ascending,temp_string)))  // No entry in list for this price already?
        insertNode(&list_by_price_ascending,temp_string,list_entry);
      else
        list_pointer->data.size += list_entry.size;
      }
    //
    if (list_entry.side[0] == 'B')  // We want to sell from highest price to lowest, so offers to buy go into this list.
      {
      sprintf(temp_string,"%0*ld",KEYLENGTH,9999999999-list_entry.price);  // NOTE: This figure of 9999999999 is still a constant associated with KEYLENGTH that should be fixed.
      if (!(list_pointer = findNode(&list_by_price_descending,temp_string)))  // No entry in list for this price already?
        insertNode(&list_by_price_descending,temp_string,list_entry);
      else
        list_pointer->data.size += list_entry.size;
      }
    //
    // Save relevant values in global variables to we can fall through to common code below.  timestamp and order_id can always be retrieved from the initial parsing pointers.
    side[0] = list_entry.side[0];
    price   = list_entry.price;
    size    = list_entry.size;
    //
    // Update the current ask/bid figures so they match the totals of the corresponding price lists.
    if (side[0] == 'B')
      current_bid_count += size;
    if (side[0] == 'S')
      current_ask_count += size;
    }
  
  if (operation_type_pointer[0] == 'R')  // Reduce/remove order.
    {
    if ((size_pointer = strtok(NULL," \n")) == NULL)     // Extract size from input line.
      {
      fputs("No size field found; continuing.\n",stderr);
      continue;
      }
    sprintf(key_string,"%*s",KEYLENGTH,order_id_pointer);  // Right-justify order id so it sorts correctly and can be used as a key.
    //
    list_pointer = findNode(&list_by_order_id,key_string);  // We need to do to this lookup to find the side and price more than anything.
    if (!list_pointer)  // Failed to look up supplied order id?
      {
      fputs("Failed to look up order id; continuing.\n",stderr);
      continue;
      }
    side[0] = list_pointer->data.side[0];             // Save these three variables.
    price   = list_pointer->data.price;               // We will need this to work with the two lists that are sorted by price.
    size    = strtol(size_pointer,(char **)NULL,10);  // The amount to reduce the order size by.
    if (size > list_pointer->data.size)  // Is pesky input data trying to reduce the order by more than its current size?
      size   = list_pointer->data.size;  // If so, then skip that BS here and just use the original amount.
    //
    // Now reduce entries in appropriate lists, or, if their sizes fall to 0, delete them.
    //
    reduce_size_or_delete_node(&list_by_order_id,key_string,size);
    //
    if (side[0] == 'S')
      {
      sprintf(temp_string,"%0*ld",KEYLENGTH,price);
      reduce_size_or_delete_node(&list_by_price_ascending,temp_string,size);
      }
    //
    if (side[0] == 'B')
      {
      sprintf(temp_string,"%0*ld",KEYLENGTH,9999999999-price);  // Again, a place where KEYLENGTH should be used instead of this 9999999999 constant.
      reduce_size_or_delete_node(&list_by_price_descending,temp_string,size);
      }
    // Update the current ask/bid figures so they match the totals of the corresponding price lists.
    if (side[0] == 'B')
      current_bid_count -= size;
    if (side[0] == 'S')
      current_ask_count -= size;
    }


  // Now, based upon what side the last add or reduce/remove operation referenced, decide what to do.
  // These two blocks of code are so much identical that I am tempted to combine them into one subroutine,
  // but we would end up passing about 5 variables to it, so I wonder if this won't suffice for now.  I'm
  // sure a more clever mechanism could be come up with for representing the two sides of the book and their
  // corresponding values and operations, but for a program as short as this one is, I'm not sure it would
  // result in significantly reduced line count, so we'll leave it as a possibility for the future right now.
  //
  if (side[0] == 'B')  // The bid counts can have changed only if this last order_id processed was a bid, so only run this code in that case.
    {
    if (current_bid_count >= target_size)
      {
      returned_price = total_price_from_list(&list_by_price_descending,target_size);
      if (returned_price != previous_bid_price)
        {
        print_cents_as_dollars(returned_price);  // This sets global variable dollar_string.
        printf("%s S %s\n",timestamp_pointer,dollar_string);
        }
      previous_bid_price = returned_price;
      }
    else
    if (previous_bid_count >= target_size)  // Bid count fell below the target size?
      {
      printf("%s S NA\n",timestamp_pointer);
      previous_bid_price = 0;
      }
    previous_bid_count = current_bid_count;  // Reset this for the next go-around.
    }

  if (side[0] == 'S')  // The ask counts can have changed only if this last order_id processed was an ask, so only run this code in that case.
    {
    if (current_ask_count >= target_size)
      {
      returned_price = total_price_from_list(&list_by_price_ascending,target_size);
      if (returned_price != previous_ask_price)
        {
        print_cents_as_dollars(returned_price);  // This sets global variable dollar_string.
        printf("%s B %s\n",timestamp_pointer,dollar_string);
        }
      previous_ask_price = returned_price;
      }
    else
    if (previous_ask_count >= target_size)  // Ask count fell below the target size?
      {
      printf("%s B NA\n",timestamp_pointer);
      previous_ask_price = 0;
      }
    previous_ask_count = current_ask_count;
    }


  if (DEBUG)  // If DEBUG is turned on, then print totals and do consistency checks after every single input line has been processed.
    {         // This code could be omitted from the final program, but is left here as an illustration of the program development process.
    printf("Current ask count: %ld\n",current_ask_count);
    printf("Current bid count: %ld\n",current_bid_count);
    //
    // Show total sizes in all three lists.
    temp_long = list_total_size(&list_by_order_id);
    printf("List by order id size total: %ld\n",temp_long);
    temp_long = list_total_size(&list_by_price_ascending);
    printf("List by price ascending size total: %ld\n",temp_long);
    temp_long = list_total_size(&list_by_price_descending);
    printf("List by price descending size total: %ld\n",temp_long);
    //
    // Check to make sure that sizes in the two price-sorted lists add up to the total size of the order-id-sorted list.
    if (list_total_size(&list_by_price_ascending) + list_total_size(&list_by_price_descending) != list_total_size(&list_by_order_id))
      fputs("ERROR: The two price lists' sizes don't add up to the order_id list's total.\n",stderr);
    // The next two statements check to make sure that the count variables we maintain never vary from the amounts in the lists, since they are, after all, duplicate data.
    if (current_ask_count != list_total_size(&list_by_price_ascending))
      fputs("ERROR: current_ask_count <> total size of list_by_price_ascending!\n",stderr);
    if (current_bid_count != list_total_size(&list_by_price_descending))
      fputs("ERROR: current_bid_count <> total size of list_by_price_descending!\n",stderr);
    //
    // Show total prices in all three lists.
    temp_long = list_total_price(&list_by_order_id);
    printf("List by order id price total: %ld\n",temp_long);
    temp_long = list_total_price(&list_by_price_ascending);
    printf("List by price ascending price total: %ld\n",temp_long);
    temp_long = list_total_price(&list_by_price_descending);
    printf("List by price descending price total: %ld\n",temp_long);
    //
    // As before, check that the total prices in the two price-sorted lists add up to the total price of the order-id-sorted list.
    if (list_total_price(&list_by_price_ascending) + list_total_price(&list_by_price_descending) != list_total_price(&list_by_order_id))
      fputs("ERROR: The two price lists' prices don't add up to the order_id list's total.\n",stderr);
    // There are no variables that hold the total prices, as there are for the counts, so nothing to check here.
    //
    printf("-----------------------------------------------------------------------\n");
    }


  // Loop back around for the next line of input!
  }

exit(0);
}

