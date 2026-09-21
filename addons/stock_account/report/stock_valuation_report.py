from collections import defaultdict

from odoo import _, api, fields, models


class StockValuationReport(models.AbstractModel):
    _name = 'stock_account.stock.valuation.report'
    _description = 'Stock Valuation'

    @api.model
    def get_report_values(self, date=False):
        return {
            'data': self.with_context(allowed_company_ids=self.env.company.ids)._get_report_data(date=date),
            'context': {},
        }

    @api.model
    def _get_report_values(self, docids, data=None):
        docs = []
        doc = self._get_report_data()
        docs.append(self._include_pdf_specifics(doc, data))
        return {
            'doc_ids': docids,
            'doc_model': 'stock.valuation.report',
            'docs': docs,
        }

    def _get_report_data(self, date=False, product_category=False, warehouse=False):
        company = self.env.company
        # Check if date is a string instance
        if isinstance(date, str):
            date = fields.Date.from_string(date)
        if date == fields.Date.context_today(self):
            date = False
        # This report is broken down by lot, so only lot-valuated products contribute:
        # their value is summed from their lots. Match the context used by total_value so
        # quantities scope to valued internal locations.
        # sudo: quantities expand kit BoMs (mrp.bom) which accounting users cannot read.
        # Kits are never valued on their own, so restrict to the valuation product domain
        # and skip the kit BoM expansion that qty_available would otherwise trigger.
        valued_product_context = self.env['product.product'].sudo().with_company(company).with_context(
            skip_kit_qty_available=True,
        )._with_valuation_context()
        if date:
            valued_product_context = valued_product_context.with_context(at_date=date, to_date=date)
        valued_products = valued_product_context.search(
            company._get_valuation_product_domain()
            + [('lot_valuated', '=', True)]
        )

        accounts_by_product = company._get_accounts_by_product(products=valued_products)

        # PERF: the report is built lot per lot, so the lots that cannot weigh on the
        # valuation are filtered out upfront. Two kinds of lots are kept: the ones still
        # holding stock, and the ones emptied but whose valuation account is not balanced,
        # as they still have a closing entry to generate. The latter are usually archived,
        # hence the `active_test=False`.
        lot_model = self.env["stock.lot"].sudo().with_company(company).with_context(active_test=False)
        if date:
            lot_model = lot_model.with_context(at_date=date, to_date=date)
        lot_ids_with_qty = self._get_lot_ids_with_stock(lot_model, valued_products, date)
        lot_ids = lot_ids_with_qty | set(
            company._get_lots_with_stock_accounting_value(accounts_by_product, at_date=date).ids
        )
        lots = lot_model.search([
            ("product_id", "in", valued_products.ids), ("id", "in", sorted(lot_ids)),
        ])

        report_data = {"sections_by_lot": []}
        # The same few valuation accounts come back on every lot: read them only once.
        accounts_data_by_id = {}
        read_account_ids = set()

        for lot in lots:
            lot_accounts_by_product = {lot.product_id: accounts_by_product[lot.product_id]}
            section_vals = {
                "lot_id": lot.id,
                "lot_name": lot.display_name,
            }
            # Only a lot kept for its stock can hold an inventory value: for the others,
            # walking their moves would just confirm a value of zero.
            inventory_data = {}
            if not date:
                if lot.id in lot_ids_with_qty:
                    inventory_data = company.stock_value(lot_accounts_by_product, lot=lot)
                accounting_data = company.stock_accounting_value(lot_accounts_by_product, lot=lot)
            else:
                if lot.id in lot_ids_with_qty:
                    inventory_data = company.stock_value(lot_accounts_by_product, at_date=date, lot=lot)
                accounting_data = company.stock_accounting_value(lot_accounts_by_product, at_date=date, lot=lot)

            accounts = inventory_data.keys() | accounting_data.keys()
            account_ids = {acc.id for acc in accounts}

            initial_balance = {
                'label': _("Initial Balance"),
                'value': 0,
                'lines_by_account_id': defaultdict(lambda: {
                    'value': 0,
                }),
            }
            ending_stock = {
                'label': _("Ending Stock"),
                'value': 0,
                'lines_by_account_id': defaultdict(lambda: {
                    'value': 0,
                }),
            }

            # Compute Opening Balance values and Ending Stock values.
            for account in accounts:
                opening_balance = accounting_data.get(account, 0)
                ending_balance = inventory_data.get(account, 0)
                account_ids.add(account.id)
                if opening_balance:
                    initial_balance['value'] += opening_balance
                    initial_balance['lines_by_account_id'][account.id]['value'] += opening_balance
                if ending_balance:
                    ending_stock['value'] += ending_balance
                    ending_stock['lines_by_account_id'][account.id]['value'] += ending_balance

            # Get accounting data.
            location_valuation_vals = company._get_location_valuation_vals(
                date, location_domain=[('usage', '=', 'inventory')], lot=lot
            )
            stock_valuation_account_vals = company.with_context(inventory_data=inventory_data)._get_stock_valuation_account_vals(
                lot_accounts_by_product, date, company._get_location_valuation_vals(date, lot=lot), lot=lot)

            section_vals.update({
                'company_id': company.id,
                'currency_id': company.currency_id.id,
                'ending_stock': ending_stock,
                'initial_balance': initial_balance,
            })

            if self._must_include_inventory_loss():
                # Compute Inventory Loss values.
                inventory_loss = {
                    'label': _("Inventory Loss"),
                    'value': 0,
                }
                lines_by_account_id = defaultdict(lambda: {
                    'debit': 0,
                    'credit': 0,
                })
                for vals in location_valuation_vals:
                    account_ids.add(vals['account_id'])
                    inventory_loss['value'] -= vals['debit']
                    lines_by_account_id[vals['account_id']]['debit'] += vals['debit']
                    lines_by_account_id[vals['account_id']]['credit'] += vals['credit']
                inventory_loss['lines'] = [{
                    'account_id': account_id,
                    'debit': vals['debit'],
                    'credit': vals['credit'],
                } for (account_id, vals) in lines_by_account_id.items()]
                section_vals['inventory_loss'] = inventory_loss

            # Compute Stock Variation values.
            stock_variation = {
                'label': _("Stock Variation"),
                'value': 0,
            }
            lines_by_account_id = defaultdict(lambda: {
                'debit': 0,
                'credit': 0,
                'lines': [],
            })
            for vals in stock_valuation_account_vals:
                account_ids.add(vals['account_id'])
                stock_variation['value'] += vals['debit']
                lines_by_account_id[vals['account_id']]['debit'] += vals['debit']
                lines_by_account_id[vals['account_id']]['credit'] += vals['credit']
            stock_variation['lines'] = [{
                'account_id': account_id,
                'debit': vals['debit'],
                'credit': vals['credit'],
            } for (account_id, vals) in lines_by_account_id.items()]

            # Lots without a Stock Variation entry have nothing to generate, so
            # they are excluded from the report regardless of any inventory loss
            # or on-hand stock.
            if not stock_variation['lines'] and company.currency_id.is_zero(stock_variation['value']):
                continue

            unread_account_ids = account_ids - read_account_ids
            if unread_account_ids:
                accounts_read_data = self.env['account.account'].search_read(
                    [('id', 'in', list(unread_account_ids))],
                    ['id', 'name', 'code', 'display_name']
                )
                accounts_data_by_id.update({acc_data['id']: acc_data for acc_data in accounts_read_data})
                read_account_ids |= unread_account_ids
            section_vals.update(
                accounts_by_id={
                    account_id: accounts_data_by_id[account_id]
                    for account_id in account_ids
                    if account_id in accounts_data_by_id
                },
                stock_variation=stock_variation,
            )
            report_data["sections_by_lot"].append(section_vals)
        return report_data

    def _get_lot_ids_with_stock(self, lot_model, valued_products, date=False):
        """ Return the ids of the lots of `valued_products` holding stock at `date`.

        The quantity on hand is read from the quants, which only tell today's stock, so for
        a past date every lot moved since then is kept as well: it may have been emptied
        after `date`. The result is a superset in that case.
        """
        lot_ids = set(lot_model.search([
            ("product_id", "in", valued_products.ids), ("product_qty", "!=", 0),
        ]).ids)
        if date:
            # `stock.lot._product_qty` compares `move_id.date` to `to_date` as a datetime:
            # a plain date would be widened to the end of the day and would drop the moves
            # of the date itself.
            lot_ids.update(
                lot.id
                for (lot,) in self.env["stock.move.line"].sudo()._read_group(
                    [
                        ("product_id", "in", valued_products.ids),
                        ("lot_id", "!=", False),
                        ("state", "=", "done"),
                        ("move_id.date", ">", fields.Datetime.to_datetime(date)),
                    ],
                    ["lot_id"],
                )
            )
        return lot_ids

    def action_print_as_pdf(self):
        return

    def action_print_as_xlsx(self):
        return

    def _must_include_inventory_loss(self):
        return bool(self.env['stock.location'].search_count([
            ('usage', '=', 'inventory'),
            ('valuation_account_id', '!=', False),
        ], limit=1))
